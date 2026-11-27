# Error-region length signatures of single-nucleotide read errors

**Setting.** In amplicon sequencing, many reads cover the same short region. For a read
$r = (r_1, \dots, r_n)$ and position $p$, let $S_k(p)$ be the $k$-mer starting at $p$ and its **k-count**
$KC_k(p)$ the number of occurrences of $S_k(p)$ over all reads (weighted by read multiplicity). Given an
error threshold $t_{\mathrm{er}}$, a $k$-mer is **solid** if its k-count exceeds $t_{\mathrm{er}}$ and **weak**
otherwise. An **error region** of $r$ is a maximal interval $x = [b, e]$ of start positions of weak
$k$-mers, with length $l(x) = e - b + 1$; it is a **tail** if it touches either end of the read
($b = 1$ or $e = n - k + 1$). Write $h_i(w)$ for a run of $i$ copies of the nucleotide $w$.

**Error types.** $\mathrm{Rep}$ is a substitution; $\mathrm{Ins}_1$ an insertion not creating a
homopolymer and $\mathrm{Ins}_p$ ($p \ge 2$) one creating a homopolymer of length $p$; $\mathrm{Del}_0$
deletes an isolated nucleotide and $\mathrm{Del}_m$ ($m \ge 1$) deletes one nucleotide from a homopolymer
of length $m + 1$.

**Lemma.** Suppose a non-tail error region $x = [b, e]$ of $r$ is caused by a single isolated
nucleotide error $E$, and let $w = r_e$. Then

1. if $E = \mathrm{Rep}$, then $l(x) = k$;
2. if $E = \mathrm{Ins}_p$ with $1 \le p \le k$, then $l(x) = k - p + 1$, and for $p \ge 2$ the region is
   followed by $h_{p-1}(w)$;
3. if $E = \mathrm{Del}_m$ with $0 \le m \le k$, then $l(x) = k - m - 1$, and for $m \ge 1$ the region is
   followed by $h_m(c)$ with $c \ne w$.

Hence a region of length $l(x) < k - 1$ determines the error type and its correction uniquely; only
$l(x) = k$ (substitution versus simple insertion) and $l(x) = k - 1$ with $r_e = r_{e+1}$ (insertion versus
deletion) are ambiguous, and are resolved by choosing the correction that creates the solid $k$-mer of
highest k-count.

**Threshold choice.** Amplicon k-count histograms are gappy, so instead of the first minimum of the
k-count frequency $f(v)$ the threshold is the end of the first sufficiently long run of consecutive
zeros of $f$.

## Depends on

- [The k-mers of a string](../../de-bruijn-graph-genome-assembly/kmers.md)

## Expansion

A substitution at position $e$ spoils exactly the $k$ windows that contain it. An inserted nucleotide
also lies in $k$ windows, but if it extends a homopolymer of the same base, sliding the window across
the run reproduces true $k$-mers for $p - 1$ of them, shortening the region to $k - p + 1$; a deletion
removes a position, so only $k - 1$ windows straddle the junction, and a shortened homopolymer again
masks $m$ of them. Matching the observed region length and the bases that follow it against these
signatures turns error correction, otherwise a minimum edit problem solvable by slow dynamic
programming, into a constant-time local decision tuned to the homopolymer errors of
pyrosequencing.

## Sources

- P. Skums, Z. Dimitrova, D. S. Campo, G. Vaughan, L. Rossi, J. C. Forbi, J. Yokosawa, A. Zelikovsky,
  Y. Khudyakov, "Efficient error correction for next-generation sequencing of viral amplicons", BMC
  Bioinformatics 13(Suppl 10) (2012) S6, Methods, k-mer based error correction, Lemma 1 and
  Algorithm 1, <https://doi.org/10.1186/1471-2105-13-s10-s6> (PMC3382444).

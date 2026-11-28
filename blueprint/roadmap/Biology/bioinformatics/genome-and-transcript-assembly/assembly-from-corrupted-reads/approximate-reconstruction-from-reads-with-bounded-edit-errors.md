# Approximate reconstruction from reads with bounded edit errors

**Model.** Let $X\in\Sigma^n$ be a uniformly random sequence over a finite alphabet $\Sigma$. Shotgun sequencing draws $N$ reads of length $L=\overline L\ln n$ at i.i.d. uniform starting positions, $R_i=X[T_i,T_i+L-1]$. Instead of $R_i$ one receives an arbitrary corrupted read $\widetilde R_i$ with edit distance $\mathrm{ed}(R_i,\widetilde R_i)\le\epsilon L$; nothing else is assumed about the error profile. An *approximate reconstruction algorithm for error rate $\epsilon$ with approximation factor $C$* outputs $\widehat X$ with $\mathrm{ed}(X,\widehat X)\le C\epsilon n$ with probability at least $1-\delta$ for large $n$. Let $N_{\mathrm{cov}}(n,L,\delta)$ be the number of reads needed to cover $X$ with probability $1-\delta$; by Lander–Waterman, $N_{\mathrm{cov}}\approx\frac nL\ln\frac{n}{L\delta}$.

**Error-free benchmark.** With $\epsilon=0$, exact reconstruction is impossible with probability above $1/2+o(1)$ if $\overline L<2/\ln|\Sigma|$, and possible with essentially $N_{\mathrm{cov}}$ reads if $\overline L>2/\ln|\Sigma|$.

**Theorem.**

1. There are constants $C,\overline C$ depending only on $|\Sigma|$ such that for every $\epsilon>0$, if $\overline L>\overline C/\epsilon$ and $N>N_{\mathrm{cov}}/\epsilon$, a simple sequential algorithm is an approximate reconstruction algorithm for error rate $\epsilon$ with approximation factor $C$.
2. For every $C>3$ there are $\overline C(\Sigma)$, $\epsilon_0(\Sigma,C)$ and $C'(\Sigma,C)$ such that for all $\epsilon\in(0,\epsilon_0)$, $\overline L\ge\overline C/\epsilon$ and $N\ge C'N_{\mathrm{cov}}/\epsilon$ suffice for approximation factor $C$.

So robust assembly, uniform over all error types, costs only a factor $1/\epsilon$ in read length and in the number of reads relative to error-free assembly.

## Depends on

- [Exact uncovered probability of a base of a linear genome](../../lander-waterman-coverage-model/lin-uncovered.md)

## Expansion

The key property of a random sequence is a shift lemma: for $\overline L$ large there is $c>0$ such that, with high probability, any two length-$L$ windows of $X$ whose starting points differ by more than a small multiple of $L$ are at edit distance at least $cL$, so corrupted reads cannot be confused with reads from distant locations. The algorithm starts from any read and repeatedly appends a read that overlaps the current right end in edit distance, extending the reconstruction; the oversampling factor $1/\epsilon$ guarantees that a suitable overlapping read always exists, and each extension contributes error proportional to $\epsilon$ times its length, giving total error $O(\epsilon n)$.

## Sources

- Shirshendu Ganguly, Elchanan Mossel, Miklós Z. Rácz, "Sequence assembly from corrupted shotgun reads", arXiv:1601.07086 (2016), Theorems 3.1–3.3 and Corollary 4.4, <https://doi.org/10.48550/arXiv.1601.07086>.

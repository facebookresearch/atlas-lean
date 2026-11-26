# Fragment-seeding sensitivity for long local alignments

**Problem.** Given a query $Q$, a reference $R$, a minimum length $l_0$ and a maximum per-base error rate $\varepsilon_{\max}$, report (approximately) every local mapping $Q[i..j]$ with $j - i + 1 \ge l_0$ that aligns to a substring of $R$ with per-base error rate $\le \varepsilon_{\max}$. Errors (substitutions and indels) are assumed to occur independently with Poisson-distributed counts, and k-mers are treated as independent, so that the Jaccard similarity of the k-mer sets of two sequences determines the expected alignment error rate (and vice versa) and an end-to-end read mapper based on MinHash estimates of that Jaccard similarity reports a true target of a read of length $\ell$ with probability $p(\ell, \varepsilon_{\max})$.

**Seeding scheme.** Split $Q$ into consecutive non-overlapping fragments of length $l_0/2$ and map each fragment end to end with threshold $\varepsilon_{\max}$.

**Statement.** Let $Q_{\mathrm{sub}}$ be a substring of $Q$ of length $|Q_{\mathrm{sub}}| \ge l_0$ that aligns to $R$ with error rate $\le \varepsilon_{\max}$. Then $Q_{\mathrm{sub}}$ fully contains at least
$$m = \Big\lfloor \frac{|Q_{\mathrm{sub}}| - l_0/2 + 1}{l_0/2} \Big\rfloor \ \ge 1$$
fragments, each of which aligns end to end within the alignment of $Q_{\mathrm{sub}}$. If each such fragment is reported at its correct target independently with probability $p$, the probability that at least one seed mapping is reported along the optimal alignment is
$$1 - (1 - p)^{m}.$$
Consecutive fragment hits $q_i, \dots, q_j$ with reference start positions $p_0 \le p_1 \le \dots \le p_{j-i}$ and gaps $p_{k+1} - p_k \le l_0$ are merged into one local alignment segment, whose boundaries are the first and last hit and whose score is the mean identity estimate times the total fragment length.

## Expansion

A window of length $|Q_{\mathrm{sub}}|$ placed anywhere on a grid of fragments of length $l_0/2$ contains every fragment whose start lies within its first $|Q_{\mathrm{sub}}| - l_0/2 + 1$ positions, and fragment starts are spaced $l_0/2$ apart, which gives the floor expression; $|Q_{\mathrm{sub}}| \ge l_0$ makes it at least $1$. Requiring each fragment to satisfy the same error-rate threshold is justified when errors are spread along the alignment at rate at most $\varepsilon_{\max}$ (the paper's per-fragment statements); a locally error-dense fragment can fail, which is absorbed into the probability $p$. Under independence the failure probability of all $m$ fragments is $(1 - p)^m$. The source reports that this bound lies between $0.92$ and $1.00$ for $\varepsilon_{\max}$ between $10\%$ and $20\%$ at the default parameters. Because only $O(|Q|/l_0)$ fragments are mapped, the cost is far below that of examining all substring pairs, which needs $\Omega(|Q||R|)$ time for exact local alignment.

## Sources

- C. Jain, S. Koren, A. Dilthey, A. M. Phillippy, S. Aluru, "A fast adaptive algorithm for computing whole-genome homology maps", Bioinformatics (2018), Section 2.1 ("Computing local alignment boundaries", 2.1.1 "Proposed algorithm") and Fig. 2, <https://doi.org/10.1093/bioinformatics/bty597> (PMC6129286).

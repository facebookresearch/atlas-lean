# Statistical query lower bound from almost uncorrelated concepts

Let $d = \mathrm{SQdim}_D(C)$, so that $C$ contains distinct concepts $f_1, \dots, f_d$ with pairwise correlations $|\mathrm{corr}_D(f_i, f_j)| \le 1/d$. Then any learning algorithm that uses tolerance parameter lower bounded by $\tau > 0$ requires in the worst case at least $(d\tau^2 - 1)/2$ queries for learning $C$ with accuracy at least $\tau$, where queries ask for correlations with the target and accuracy is the correlation of the output hypothesis with the target (Szörényi, Theorem 5). For $\tau = 1/\sqrt[3]{d}$ this means $(\sqrt[3]{d} - 1)/2$ queries.

## Proof sketch

Answer each query function $h$, of norm at most $1$, by $0$. With $A = \{i : \langle f_i, h\rangle \ge \tau\}$, the Cauchy-Schwarz inequality and the pairwise correlation bound give $\langle h, \sum_{i \in A} f_i\rangle^2 \le |A| + |A|^2/d$, while the choice of $A$ gives $\langle h, \sum_{i \in A} f_i\rangle \ge |A|\tau$; hence $|A| \le d/(d\tau^2 - 1)$, and the same holds for the concepts with correlation at most $-\tau$. Each query eliminates at most $2d/(d\tau^2 - 1)$ of the $d$ concepts (proof of Theorem 5).

Derived (not stated in the cited sources): let concepts $f_i \in C$, $i \in \kappa$, have pairwise correlations $|\mathrm{corr}_D(f_i, f_j)| \le \gamma$ under $D$, and let a learner learn $C$ under $D$ (statelessly) with tolerance $\tau \ge 0$ and error $\varepsilon \in [0, 1/2]$ using at most $q$ queries, where $\gamma < \tau^2$ and $\gamma < (1-2\varepsilon)^2$. Then $|\kappa| \le \frac{q(1-\gamma)}{\tau^2 - \gamma} + \frac{1-\gamma}{(1-2\varepsilon)^2 - \gamma}$, and if only $\mathrm{corr}_D(f_i, f_j) \le \gamma$ is assumed, the same holds with $2q$ in place of $q$. Write a query as $\phi(x, y) = g(x) + k(x)\,y^{\pm}$ with $|k| \le 1$ and answer it by $\mathbb{E}_D g$; this answer is valid for every $f_i$ except those with $|\mathbb{E}_D[k f_i]| > \tau$, and Bessel's inequality for almost orthogonal vectors $(\sqrt{D(x)} f_i(x))_x$ bounds their number by $(1-\gamma)/(\tau^2 - \gamma)$, while the single output hypothesis must have correlation at least $1 - 2\varepsilon$ with all remaining concepts, which bounds them by $(1-\gamma)/((1-2\varepsilon)^2 - \gamma)$.

## Depends on

- [Statistical query model with tolerance and the SQ dimension](statistical-query-dimension.md)

## Sources

- A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour and S. Rudich, "Weakly Learning DNF and Characterizing Statistical Query Learning Using Fourier Analysis", Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing (STOC), 1994.
- B. Szorenyi, "Characterizing Statistical Query Learning: Simplified Notions and Proofs", Algorithmic Learning Theory (ALT), 2009, Definition 4 and Theorem 5; open copy: <http://www.inf.u-szeged.hu/~szorenyi/Cikkek/sq_d0_ext.pdf>.
- L. Reyzin, "Statistical Queries and Statistical Algorithms: Foundations and Applications", arXiv preprint, 2020.

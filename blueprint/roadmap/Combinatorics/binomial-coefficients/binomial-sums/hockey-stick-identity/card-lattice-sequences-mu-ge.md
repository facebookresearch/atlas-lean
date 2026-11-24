# Counting lattice sequences by the statistics omega and mu

Let $r, k, n, i$ be natural numbers with $i \le k$, and put $\eta = rk + n + 1$. The number of lattice sequences $L \in \mathcal{L}(\eta, k)$, that is, $0 = L_0 \le L_1 \le \dots \le L_{\eta+1} = k$, with

$$r\, \omega_\eta(L) \le \mu_\eta(L) \quad\text{and}\quad \omega_\eta(L) = k - i$$

is $\binom{(r+1)i + n}{i}$. Here $\omega_\eta(L) = L_{\eta+1} - L_\eta$, and $\mu_\eta(L) = \eta - 1 - \gamma_\eta(L)$ with $\gamma_\eta(L)$ the largest $j < \eta$ such that $L_j < L_{j+1}$, or $-1$ if there is none.

## Sources

- Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, J. Integer Seq. 28 (2025), Article 25.7.7, Lemma 9, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Weselcouch/wesel8.html>.

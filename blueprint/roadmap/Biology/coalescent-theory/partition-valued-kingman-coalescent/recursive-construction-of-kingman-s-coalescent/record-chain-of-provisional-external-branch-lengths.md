# Record chain of provisional external branch lengths in Kingman's coalescent

**Setting.** Build Kingman's coalescent recursively: given the $n$-coalescent $\Pi^n$, individual $n+1$ attaches at rate $|\Pi^n(t)|$ (the current number of blocks) to a uniformly chosen block, at time $L_{n+1}$, so

$$\mathbb P(L_{n+1} \ge t \mid \Pi^n) = \exp\Big(-\int_0^t |\Pi^n(s)|\,ds\Big).$$

$L_n$ is the provisional external branch length of individual $n$; the sequence $(L_n)_{n\ge2}$ is not Markov. Let $A_1$ be the index of the largest $L_n$, and recursively let $A_i$ be the index of the largest $L_n$ with $n > A_{i-1}$; let $R_i$ be the rank of $L_{A_i}$ among all $(L_n)_{n\ge2}$ (so $R_1 = 1$).

**Theorem.** $(R_i, A_i)_{i\ge1}$ is a Markov chain with $A_i - R_i \ge 1$,

$$\mathbb P(A_1 = n) = \frac{2}{n(n+1)}, \quad n \ge 2,$$

and transitions, for $1 \le x \le A_i - R_i$ and $y \ge 1$,

$$\mathbb P(R_{i+1} \ge R_i + x \mid R_i, A_i) = \frac{\binom{2A_i - 1}{A_i - R_i - x}}{\binom{2A_i - 1}{A_i - R_i - 1}}, \qquad \mathbb P(A_{i+1} \ge A_i + y \mid R_i, A_i, R_{i+1}) = \frac{A_i + R_{i+1}}{A_i + R_{i+1} + y - 1}.$$

Moreover, the rescaled process $\big(R_{n+1+i}^2/A_{n+1+i},\ A_{n+i}/A_{n+1+i}\big)_{i\ge1}$ converges in finite-dimensional distributions as $n \to \infty$ to the stationary Markov chain $(\xi_i, \eta_i)_{i\ge1}$ given by $\xi_i = (\xi_{i-1} + X_i)\eta_i$ with $\xi_0, X_i \sim \mathrm{Exp}(1)$ and $\eta_i \sim \mathrm{Unif}(0,1)$ independent; its marginals are $\xi_i \sim \mathrm{Exp}(1)$ and $(\xi_1,\eta_1)$ has density $\frac{s}{t^2}e^{-s/t}$ on $s \ge 0$, $0 < t < 1$.

## Expansion

The proof uses Aldous's construction of Kingman's coalescent from a sequence of i.i.d. points in which the attachment of individual $n+1$ is encoded by the relative order of fresh uniform variables, so record-type statistics of $(L_n)$ reduce to exchangeable combinatorics. Summing the law of $A_1$ gives $\mathbb P(A_1 \ge n) = 2/n$, so the index of the longest provisional external branch has a heavy tail. The scaling limit shows records arrive geometrically, with $A_{i}/A_{i+1}$ asymptotically uniform.

## Sources

- Linglong Yuan, "On a Markov chain related to the individual lengths in the recursive construction of Kingman’s coalescent", ALEA Lat. Am. J. Probab. Math. Stat. 21 (2024), 725, <https://doi.org/10.30757/ALEA.v21-28>. Numbering follows the arXiv version, arXiv:2310.14882 (2023): Section 2 (main Markov-chain theorem and its scaling-limit theorem), <https://doi.org/10.48550/arXiv.2310.14882>.

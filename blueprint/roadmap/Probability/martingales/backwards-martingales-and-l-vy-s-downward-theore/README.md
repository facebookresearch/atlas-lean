# Backwards martingale convergence theorem

Let $(\Omega, \mathcal{F}, \mu)$ be a probability space, let $\mathcal{F}_0 \supseteq \mathcal{F}_1 \supseteq \cdots$ be a decreasing sequence of sub-σ-algebras of $\mathcal{F}$, and let $\mathcal{F}_\infty = \bigcap_n \mathcal{F}_n$. Let $(M_n)_{n \ge 0}$ be a real-valued backwards martingale: $M_0$ is integrable and $M_n = \mathbb{E}[M_0 \mid \mathcal{F}_n]$ almost everywhere for every $n$. Then $M_n \to \mathbb{E}[M_0 \mid \mathcal{F}_\infty]$ almost everywhere as $n \to \infty$.

## Idea

In an ordinary martingale information grows with time; in a backwards martingale it shrinks, and each term is the best estimate of $M_0$ from coarser information. Unlike the forward theorem, no boundedness hypothesis is needed: every term is a conditional expectation of the single integrable variable $M_0$, so the family is uniformly integrable, and the convergence also holds in $L^1$. A standard proof counts upcrossings: read backwards, $M_N, M_{N-1}, \dots, M_0$ is a forward martingale, and Doob's upcrossing inequality bounds the expected number of crossings of any interval uniformly in $N$. Uniform integrability then upgrades the convergence to convergence in $L^1$. The limit is $\mathcal{F}_\infty$-measurable, and passing to the limit in $\int_A M_n = \int_A M_0$, for $A \in \mathcal{F}_\infty$, identifies it as $\mathbb{E}[M_0 \mid \mathcal{F}_\infty]$. Lévy's downward theorem is the case $M_n = \mathbb{E}[g \mid \mathcal{F}_n]$. For independent identically distributed integrable $X_1, X_2, \dots$ with $S_n = X_1 + \dots + X_n$, conditioning on $\sigma(S_n, S_{n+1}, \dots)$ gives $\mathbb{E}[X_1 \mid S_n, S_{n+1}, \dots] = S_n / n$, and the theorem, together with the Hewitt–Savage zero–one law, which makes the limit the constant $\mathbb{E}[X_1]$, yields the strong law of large numbers.

## Statements

- [Backwards martingale convergence theorem, almost sure convergence](backwards-martingale-ae-tendsto.md)
- [Backwards martingale convergence theorem in L¹](backwards-martingale-tendsto-e-lp-norm-o.md): $L^1$ convergence
- [Lévy's downward theorem, almost sure convergence](levy-downward-ae.md): Lévy's downward theorem: case of conditional expectations
- [Lévy's downward theorem in L¹](levy-downward-tendsto-e-lp-norm-one.md): Lévy's downward theorem in $L^1$
- [Backwards martingale](is-backwards-martingale.md): definition used in the main statement
- [Terms of a backwards martingale are integrable](integrable.md): basic property of backwards martingales
- [Conditioning a backwards martingale on the next level](cond-exp-succ-ae-eq.md): basic property of backwards martingales
- [Backwards martingales are uniformly integrable](uniform-integrable.md): basic property: uniform integrability, behind the $L^1$ convergence
- [Conditional expectations form a backwards martingale](is-backwards-martingale-cond-exp.md): example: conditional expectations along a decreasing filtration, the backwards martingales of Lévy's theorem
- [Conditional expectations along a filtration are strongly adapted](strongly-adapted-cond-exp.md): basic property of the conditional expectations in Lévy's theorem: adaptedness
- [Identifying the a.e. limit of conditional expectations](cond-exp-antitone-limit-eq.md): a step of the classical proof of Lévy's downward theorem: it identifies the almost-everywhere limit of the conditional expectations
- [Almost-everywhere convergent conditional expectations converge in L¹](tendsto-e-lp-norm-cond-exp-sub-of-ae-ten.md): a step of the classical proof of the $L^1$ form of Lévy's theorem: almost-everywhere convergence of conditional expectations upgrades to $L^1$ convergence
- [Tail sigma-algebra of a decreasing filtration](tail-algebra.md): definition of the limit σ-algebra
- [Tail sigma-algebra of a constant filtration](tail-algebra-const.md): basic property of the limit σ-algebra
- [Tail sigma-algebra lies in the ambient sigma-algebra](tail-algebra-le.md): basic property of the limit σ-algebra
- [Tail sigma-algebra lies in every level of the filtration](tail-algebra-le-seq.md): basic property of the limit σ-algebra

## Background

- [Martingale convergence theorem](../martingale-convergence-theorems/README.md)

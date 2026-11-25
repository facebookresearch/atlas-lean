# Weak SDE representation of one-dimensional martingale-problem solutions

Let $I\subseteq\mathbb R$ be an interval, let $a,b:I\to\mathbb R$ be continuous with $a\ge0$, and let $Af=bf'+\frac12af''$. Let $X$ be a continuous $I$-valued process that solves the [martingale problem](../../markov-chains/martingale-problems/martingale-problems-generic-definition.md) for $A$ with respect to a filtration $(\mathcal F_t)$ for every $f\in C_c^2(\mathbb R)$ restricted to $I$ (for compact $I$, for every $f\in C^2(I)$). Then

$$M_t=X_t-X_0-\int_0^tb(X_s)\,ds$$

is a [continuous local martingale](../../martingales/quadratic-variation-of-continuous-local-martingales/local-martingales-and-localization.md) with [quadratic variation](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md) $\langle M\rangle_t=\int_0^ta(X_s)\,ds$. Moreover, on the product of the underlying space with a space carrying an independent Brownian motion $W'$, with the product filtration replaced by its [usual augmentation](../../martingales/stopping-times-and-martingale-problems/martingales-and-martingale-problems-are-preserve.md), the process

$$W_t=\int_0^t a(X_s)^{-1/2}\,\mathbf 1_{\{a(X_s)>0\}}\,dM_s+\int_0^t\mathbf 1_{\{a(X_s)=0\}}\,dW'_s$$

is a Brownian motion, by [Lévy's characterization](../construction-and-sample-paths-of-brownian-motion/levy-characterization-of-brownian-motion.md), and

$$X_t=X_0+\int_0^tb(X_s)\,ds+\int_0^t\sqrt{a(X_s)}\,dW_s ,$$

so $X$ is a weak solution of the corresponding SDE.

## Depends on

- [Martingale problems (generic definition)](../../markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Local martingales and localization](../../martingales/quadratic-variation-of-continuous-local-martingales/local-martingales-and-localization.md)
- [Quadratic variation of continuous local martingales](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md)
- [Stochastic integral against continuous local martingales (localized)](../it-integral/stochastic-integral-against-continuous-local-mar.md)
- [Martingales and martingale problems are preserved by the usual augmentation](../../martingales/stopping-times-and-martingale-problems/martingales-and-martingale-problems-are-preserve.md)
- [Lévy characterization of Brownian motion](../construction-and-sample-paths-of-brownian-motion/levy-characterization-of-brownian-motion.md)

## Expansion

A full proof applies the martingale property to cutoffs of $f(x)=x$ and $f(x)=x^2$, localized at exit times of compact subintervals of $I$, to identify $M$ and $\langle M\rangle$; checks that the two integrands in $W$ are admissible and that $\langle W\rangle_t=t$; and verifies $\int\sqrt{a(X)}\,dW=M$ because $\int\mathbf 1_{\{a(X)=0\}}\,d\langle M\rangle=0$. It should check:

- the full test domain is needed: on the domain spanned by $1$ and $x$, Brownian motion stopped at a hitting time solves the zero operator, and with such a domain the conclusion $dX=0$ would be false;
- for Feller's diffusion, $a(x)=\gamma x$ vanishes at $0$, and the enlargement by $W'$ handles the set $\{a(X)=0\}$.

## Sources

- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Grundlehren 233, Springer, 1979, <https://books.google.com/books?id=vKC1BwAAQBAJ>, weak solutions from martingale problems.
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, 1991, <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, martingale problem and weak solutions (Ch. 5, topic).

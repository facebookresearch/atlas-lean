# Cherries and tridents of uniform ranked tree-child networks

**Setting.** Let $\nu_\ell$ be a uniformly random ranked tree-child network (RTCN) on $\ell$ labeled leaves. A *cherry* is a pair of leaves with a common parent; a *trident* (reticulated cherry) is a triple of leaves whose parents form a reticulation pattern created by a single reticulation event. Let $\kappa_\ell$ and $\chi_\ell$ be the numbers of cherries and tridents of $\nu_\ell$.

**Theorem (cherries).** For $\ell=2$ the network is a single cherry, so $\kappa_2=1$ and $\mathbb E[\kappa_2]=1$. For all $\ell \ge 3$,

$$\mathbb E[\kappa_\ell] = \frac{(3\ell-5)\,\ell}{12(\ell-1)(\ell-2)}$$

(the right side is undefined at $\ell=2$). The factorial moments satisfy $\mathbb E[\kappa_\ell(\kappa_\ell-1)\cdots(\kappa_\ell-n+1)] \to 4^{-n}$, and hence

$$\kappa_\ell \xrightarrow[\ell\to\infty]{d} \mathrm{Poisson}(1/4).$$

The factorial moments $m^n_\ell$ obey $m^n_{\ell+1} = \big(\frac{\ell-2n}{\ell}\big)^2 m^n_\ell + \frac{n(\ell-2n+2)}{\ell^2}\,m^{n-1}_\ell$.

**Proposition (tridents).** The mean $\mu_\ell = \mathbb E[\chi_\ell]$ satisfies

$$\mu_{\ell+1} = \Big(\frac{\ell-3}{\ell}\Big)^2\mu_\ell + \frac{\ell-1}{\ell},$$

so $\mu_2 = 0$, $\mu_3 = 1/2$, $\mu_4 = 2/3$ and, for $\ell \ge 4$,

$$\mu_\ell = \frac{(15\ell^3 - 85\ell^2 + 144\ell - 71)\,\ell}{105(\ell-1)(\ell-2)(\ell-3)}, \qquad \operatorname{Var}(\chi_\ell) = \frac{24}{637}\,\ell + \frac1{21} + o(1).$$

Thus a uniform RTCN has only $O(1)$ cherries but about $\ell/7$ tridents, in contrast with uniform ranked trees, which have about $\ell/3$ cherries.

## Depends on

- [Enumeration of ranked tree-child networks](enumeration-of-ranked-tree-child-networks.md)

## Expansion

The proof couples $\kappa_\ell$ (resp. $\chi_\ell$) with an explicit Markov chain indexed by $\ell$, obtained by reading the uniform backward coalescence–reticulation construction one event at a time; conditioning on the last event yields the linear recursions for factorial moments. The cherry recursion has a creation term of order $1/\ell$ and destruction factor $(1-2n/\ell)^2$, so $m^n_\ell$ converges to $4^{-n}$ and the Poisson limit follows by the method of moments; the trident recursion has an order-one creation term, hence linear growth of the mean.

## Sources

- François Bienvenu, Amaury Lambert and Mike Steel, "Combinatorial and stochastic properties of ranked tree-child networks", arXiv:2007.09701 (2020), Section 4: Theorem 4.2 (limits of cherries and tridents), Propositions 4.3–4.5 (cherry Markov chain and moments), Propositions 4.6–4.8 (tridents), <https://doi.org/10.48550/arXiv.2007.09701>.

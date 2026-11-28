# Closed-form solution of continuous-time single-crossover recombination

Sites are $S = \{0,1,\dots,n\}$, each site $i$ carries a letter from a finite set $X_i$, and types are sequences $x = (x_0,\dots,x_n) \in X = X_0 \times \dots \times X_n$. The links between neighbouring sites form $L = \{\tfrac12, \tfrac32, \dots, \tfrac{2n-1}{2}\}$, link $\alpha = \tfrac{2i+1}{2}$ lying between sites $i$ and $i+1$. For a population, i.e. a non-negative measure $\omega$ on $X$, let $\pi_{<\alpha}.\omega$ and $\pi_{>\alpha}.\omega$ be its marginals on the sites before and after $\alpha$. The **recombinator** at $\alpha$ is

$$R_\alpha(\omega) = \frac{1}{\|\omega\|}\, (\pi_{<\alpha}.\omega) \otimes (\pi_{>\alpha}.\omega),$$

the population obtained when every individual is cut at $\alpha$ and leading and trailing segments are relinked at random. Recombinators are idempotent and commute, so the composite recombinators $R_G = \prod_{\alpha\in G} R_\alpha$, $G \subseteq L$ (with $R_\varnothing$ the identity), satisfy $R_G R_H = R_{G\cup H}$.

In continuous time each individual undergoes a crossover at link $\alpha$ at rate $\varrho_\alpha > 0$, exchanging the sites after $\alpha$ with a random partner. In an infinite population this gives the **single-crossover recombination equation**

$$\dot\omega_t = \sum_{\alpha \in L} \varrho_\alpha \big( R_\alpha(\omega_t) - \omega_t \big),$$

a large nonlinear system of ordinary differential equations.

**Theorem (Baake, Theorem 1).** The solution with initial value $\omega_0$ is

$$\omega_t = \sum_{G \subseteq L} a_G(t)\, R_G(\omega_0), \qquad a_G(t) = \prod_{\alpha \in L\setminus G} e^{-\varrho_\alpha t} \prod_{\beta \in G} \big(1 - e^{-\varrho_\beta t}\big).$$

The coefficient $a_G(t)$ is the probability that the set of links of a given sequence that have seen at least one crossover by time $t$ is exactly $G$; its product form says the links act independently. As $t \to \infty$, $\omega_t$ converges to $\|\omega_0\|^{-n}$ times the product of the $n+1$ single-site marginals of $\omega_0$ (linkage equilibrium).

**Theorem (Baake, Theorem 2; underlying linearity).** Let $c^{(L')}_{G'}(t)$, $G' \subseteq L' \subseteq L$, be non-negative functions with $\sum_{H \subseteq L'} c^{(L')}_H(t) = 1$ and $c^{(L)}_G = c^{(L_1)}_{G\cap L_1}\, c^{(L_2)}_{G \cap L_2}$ for every partition $L = L_1 \cup L_2$. Then for every non-negative measure $v$ and $H \subseteq L$,

$$R_H\Big( \sum_{G \subseteq L} c^{(L)}_G(t)\, R_G(v) \Big) = \sum_{G \subseteq L} c^{(L)}_G(t)\, R_{G\cup H}(v).$$

The coefficients $a_G$ satisfy these conditions, so the recombinators act linearly along solutions, and the flow $\varphi_t$ commutes with every $R_G$: $R_G \circ \varphi_t = \varphi_t \circ R_G$.

## Depends on

- [Random mating with recombination](../recombine.md)

## Expansion

Write the candidate solution as $\varphi_t(\omega_0) = \sum_G a_G(t) R_G(\omega_0)$. Differentiating the product form gives $\dot a_G = \sum_{\beta\in G} \varrho_\beta\, a_{G\setminus\{\beta\}} - \big(\sum_{\alpha\notin G}\varrho_\alpha\big) a_G$. The linearity identity gives $R_\alpha(\varphi_t(\omega_0)) = \sum_K a_K(t) R_{K\cup\{\alpha\}}(\omega_0)$, so the coefficient of $R_G(\omega_0)$ on the right-hand side of the equation is $\sum_{\alpha\in G}\varrho_\alpha (a_G + a_{G\setminus\{\alpha\}}) - \sum_{\alpha}\varrho_\alpha a_G$, which is the same expression. The linearity identity itself comes from the fact that recombination at or after $\alpha$ does not change marginals before $\alpha$ and vice versa, so a product-form mixture of composite recombinators is mapped by $R_H$ term by term.

## Sources

- E. Baake, *Deterministic and stochastic aspects of single-crossover recombination*, in *Proceedings of the International Congress of Mathematicians 2010 (ICM 2010)*, Vol. IV (2011), 3037–3053, <https://doi.org/10.1142/9789814324359_0178>; preprint arXiv:1101.2081, <https://doi.org/10.48550/arXiv.1101.2081>.

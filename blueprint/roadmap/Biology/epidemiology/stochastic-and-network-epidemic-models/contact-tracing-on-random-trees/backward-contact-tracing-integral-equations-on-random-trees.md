# Backward contact-tracing integral equations on random trees

**Model.** A stochastic SIR epidemic spreads on a rooted random tree in which every node has an i.i.d. number $K$ of downstream edges, with probability generating function $G(s)=\mathbb{E}[s^K]$; initially only the root is infected. Along each edge, contacts occur at rate $\beta$ and transmit from infected to susceptible. An infected individual recovers undetected at rate $\alpha$ or is diagnosed at rate $\sigma$; a diagnosed individual becomes an index case, and each infected neighbor of an index case is found with probability $p$. In **backward** tracing an individual can be found only through its infectees (downstream index cases). In **recursive** tracing, traced individuals become index cases too; in **one-step** tracing they do not. Let $\kappa^-(a)$ be the probability that an infected individual is still infectious at infection age $a$; without tracing it is $\hat\kappa(a)=e^{-(\alpha+\sigma)a}$.

**Theorem.** Under backward tracing, $\kappa^-$ does not depend on the generation and satisfies:

*(1)* *(Recursive.)*

$$\kappa_r^-(a)=e^{-(\alpha+\sigma)a}\,G\!\left(1-p\int_0^a\big[1-e^{-\beta(a-\tilde a)}\big]\Big[-\tfrac{d}{d\tilde a}\kappa_r^-(\tilde a)-\alpha\kappa_r^-(\tilde a)\Big]\,d\tilde a\right).$$

*(2)* *(One-step.)*

$$\kappa_o^-(a)=e^{-(\alpha+\sigma)a}\,G\!\left(1-p\int_0^a\big[1-e^{-\beta(a-\tilde a)}\big]\,\sigma\,\kappa_o^-(\tilde a)\,d\tilde a\right).$$

*(3)* *(First order in $p$.)* For $\beta\ne\alpha+\sigma$ and $K$ with finite moments, both modes agree to first order:

$$\kappa^-(a)=\hat\kappa(a)\left(1+\frac{p\sigma\,\mathbb{E}K}{\alpha+\sigma-\beta}\big(e^{-\beta a}-\hat\kappa(a)\big)-\frac{p\sigma\,\mathbb{E}K}{\alpha+\sigma}\big(1-\hat\kappa(a)\big)\right)+O(p^2).$$

Analogous recursions hold for forward tracing (found through one's infector, now generation-dependent), and the full process combines the two; the homogeneously mixing results are recovered as a limit.

## Expansion

Condition on the focal individual's $k$ downstream edges. On one edge the first contact happens at age $\tilde a$ with density $\beta e^{-\beta\tilde a}$, after which the contactee is an infected individual of the next generation with the same law. The focal individual is traced in $[0,a]$ through that edge if the contactee stops being infectious by diagnosis (one-step: rate $\sigma\kappa$) or by diagnosis or tracing (recursive: the total exit rate $-\kappa'$ minus undetected recovery $\alpha\kappa$) and the edge is traced with probability $p$. Edges act independently, so the probability of no tracing event is the $k$-th power of the one-edge probability, and averaging over $K$ produces $G$. The two modes differ only at order $p^2$ because tracing along a path of two edges needs two successful tracing events.

## Sources

- Augustine Okolie and Johannes Müller, "Exact and approximate formulas for contact tracing on random trees", arXiv:1910.06860 (2019), Section 2.1, Theorems 2.1 and 2.3, Proposition 2.4 and Theorem 2.8 (forward tracing), <https://doi.org/10.48550/arXiv.1910.06860>.

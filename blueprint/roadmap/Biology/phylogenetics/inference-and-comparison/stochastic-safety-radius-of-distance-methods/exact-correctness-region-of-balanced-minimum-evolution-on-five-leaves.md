# Exact correctness region of balanced minimum evolution on five leaves

**Balanced minimum evolution (BME).** For a dissimilarity vector $\delta = (\delta_{xy})$ on leaves $X = [n]$ and a binary tree $t$, let $\mathbf x_{xy}(t) = 2^{\,n-2-l(x,y)}$, where $l(x,y)$ is the number of internal vertices on the path between leaves $x$ and $y$ (Pauplin's coefficients scaled by $2^{n-2}$). The BME tree is the binary tree minimizing $\delta\cdot\mathbf x(t)$.

**Random errors model.** The input is $\delta_{xy} = d_{xy} + \epsilon_{xy}$, where $d = d_T$ is the tree metric of a binary tree $T$ with branch lengths and the $\epsilon_{xy}$ are i.i.d. $N(0,\sigma^2)$. A method has **$\eta$-stochastic safety radius** $s_n$ if, with $\sigma^2 = c^2/\log n$, every binary $T$ with minimum interior edge length $w_{\min}$ satisfies $c < s_n w_{\min} \Rightarrow \mathbb P(M(\delta) = T) \ge 1-\eta$.

**Theorem.** Let $T$ be a binary tree on five leaves $\{a,b,c,d,e\}$ with cherries $\{a,b\}$ and $\{d,e\}$, middle leaf $c$, and interior edge lengths $w_1$ (the edge above $\{a,b\}$) and $w_2$ (the edge above $\{d,e\}$). (Theorem 3 of the source describes the tree with cherries $\{a,b\}$ and $\{c,d\}$, but its inequalities are the BME region of $((a,b),c,(d,e))$: comparing the BME lengths of all $15$ five-leaf trees with Pauplin weights reproduces exactly the five inequalities below for this tree.) Put

$$y_1 = 2\epsilon_{ac} + \epsilon_{ad} - \epsilon_{bc} + \epsilon_{bd} + 3\epsilon_{be} - \epsilon_{ce}, \qquad y_2 = 2\epsilon_{ac} + \epsilon_{ae} - \epsilon_{bc} + 3\epsilon_{bd} + \epsilon_{be} - \epsilon_{cd},$$

$$y_3 = -\epsilon_{ac} + \epsilon_{ad} + 3\epsilon_{ae} + 2\epsilon_{bc} + \epsilon_{bd} - \epsilon_{ce}, \qquad y_4 = -\epsilon_{ac} + 3\epsilon_{ad} + \epsilon_{ae} + 2\epsilon_{bc} + \epsilon_{be} - \epsilon_{cd},$$

$$z_1 = -\epsilon_{ac} + 3\epsilon_{ad} + \epsilon_{bd} + \epsilon_{be} - \epsilon_{cd} + 2\epsilon_{ce}, \qquad z_2 = -\epsilon_{ac} + 3\epsilon_{ae} + \epsilon_{bd} + \epsilon_{be} + 2\epsilon_{cd} - \epsilon_{ce},$$

$$z_3 = \epsilon_{ad} + \epsilon_{ae} - \epsilon_{bc} + 3\epsilon_{bd} - \epsilon_{cd} + 2\epsilon_{ce}, \qquad z_4 = \epsilon_{ad} + \epsilon_{ae} - \epsilon_{bc} + 3\epsilon_{be} + 2\epsilon_{cd} - \epsilon_{ce}.$$

Then BME returns the correct tree $T$ if and only if all five inequalities hold:

$$4w_2 > \epsilon_{ac} + \epsilon_{bc} + 2\epsilon_{de} - \min(\epsilon_{ad} + \epsilon_{bd} + 2\epsilon_{ce},\ \epsilon_{ae} + \epsilon_{be} + 2\epsilon_{cd}),$$

$$6w_1 + 4w_2 > 3\epsilon_{ab} + 2\epsilon_{de} - \min(y_1,y_2,y_3,y_4),$$

$$6w_1 + 6w_2 > 3\epsilon_{ab} + 3\epsilon_{de} - \min(3\epsilon_{ae} + 3\epsilon_{bd},\ 3\epsilon_{ad} + 3\epsilon_{be}),$$

$$4w_1 + 6w_2 > 2\epsilon_{ab} + 3\epsilon_{de} - \min(z_1,z_2,z_3,z_4),$$

$$4w_1 > 2\epsilon_{ab} + \epsilon_{cd} + \epsilon_{ce} - \min(\epsilon_{ad} + \epsilon_{ae} + 2\epsilon_{bc},\ 2\epsilon_{ac} + \epsilon_{bd} + \epsilon_{be}).$$

Since the errors are Gaussian, the probability that BME is correct is the Gaussian measure of this polyhedral region, which is how the five-leaf stochastic safety radius of BME is computed.

## Expansion

With five leaves there are $15$ binary trees, and BME picks $T$ exactly when $\delta\cdot\mathbf x(T) < \delta\cdot\mathbf x(t)$ for the $14$ others. Substituting $\delta = d_T + \epsilon$, the tree-metric part of each difference reduces, by Pauplin's formula, to a positive combination of the interior edge lengths, and the error part is a linear form in $\epsilon$. Grouping the $14$ competitors by the interior-edge combination that appears and keeping the binding constraint in each group gives the five inequalities with the minima. The analogous neighbor-joining analysis tracks the cherry choices of each agglomeration step.

## Depends on

- [Pauplin's formula: BME length equals tree length](../../pauplin-s-formula-and-balanced-minimum-evolution/bme-length-eq-length.md)

## Sources

- Jing Xi, Jin Xie, Ruriko Yoshida, Stefan Forcey, "Stochastic safety radius on neighbor-joining method and balanced minimal evolution on small trees", arXiv (2015). Definitions 1–2 (safety radius, stochastic safety radius), Section 3 (Theorem 3, BME on five leaves), Section 4 (neighbor-joining). <https://doi.org/10.48550/arXiv.1507.08734>. Published version: Proceedings of the 10th Workshop on Uncertainty Processing (WUPES 2015), Moninec, 217–230 (no DOI); locators above refer to the arXiv version.

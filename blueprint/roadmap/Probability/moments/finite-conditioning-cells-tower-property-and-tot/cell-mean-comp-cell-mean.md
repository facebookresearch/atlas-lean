# Nested tower property

**Nested tower property.** Let $\alpha$ and $C$ be finite sets, $p : \alpha \to \mathbb{R}$ with $p(x) \ge 0$ for all $x$, $G : \alpha \to C$, $f : C \to D$, $Y : \alpha \to \mathbb{R}$ and $d \in D$. For an observation $H$ write $E_p[Z \mid H = h] = \big(\sum_{x : H(x) = h} p(x) Z(x)\big) / \sum_{x : H(x) = h} p(x)$, with $t / 0 = 0$. Then conditioning first on the cells of $G$ and then on the coarser cells of $f \circ G$ is conditioning on $f \circ G$:

$$E_p\big[\, E_p[Y \mid G = G(\cdot)\,] \;\big|\; f(G) = d \big] = E_p[Y \mid f(G) = d].$$

This holds for every $d$, including cells of mass $0$, where both sides are $0$.

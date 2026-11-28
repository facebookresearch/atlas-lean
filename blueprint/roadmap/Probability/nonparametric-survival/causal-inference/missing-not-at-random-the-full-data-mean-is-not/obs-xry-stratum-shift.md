# Obs XRY stratum Shift

Let $\mathcal X$ be a set, and for $(x, r, y) \in \mathcal X \times \{0,1\} \times \mathbb R$ let $o(x, r, y) = (x, r, y)$ if $r = 1$ and $(x, 0, 0)$ if $r = 0$ be the observed data. For $x_0 \in \mathcal X$ and $c \in \mathbb R$ let $s_{x_0, c}$ be the stratum shift

$$s_{x_0, c}(x, r, y) = \begin{cases} (x, r, y + c) & x = x_0 \text{ and } r = 0, \\ (x, r, y) & \text{otherwise.} \end{cases}$$

Then $o(s_{x_0, c}(z)) = o(z)$ for every $z$: the stratum shift does not change the observed data.

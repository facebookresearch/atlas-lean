# Stratum Shift

For a covariate value $x_0 \in \mathcal X$ and $c \in \mathbb R$, the stratum shift $s_{x_0, c} : \mathcal X \times \{0,1\} \times \mathbb R \to \mathcal X \times \{0,1\} \times \mathbb R$ adds $c$ to the outcome of the nonrespondents ($r = 0$) in the covariate stratum $x = x_0$ and leaves every other point unchanged:

$$s_{x_0, c}(x, r, y) = \begin{cases} (x, r, y + c) & x = x_0 \text{ and } r = 0, \\ (x, r, y) & \text{otherwise.} \end{cases}$$

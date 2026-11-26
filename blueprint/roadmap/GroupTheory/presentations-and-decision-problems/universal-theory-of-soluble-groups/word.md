# Group words in countably many variables

A word in the variables $x_0, x_1, x_2, \dots$ is a finite list of letters $(i, b)$ with $i \in \mathbb{N}$ and $b \in \{\mathrm{true}, \mathrm{false}\}$. The letter $(i, \mathrm{true})$ stands for $x_i$ and the letter $(i, \mathrm{false})$ for $x_i^{-1}$, and a list $(i_1, b_1), \dots, (i_m, b_m)$ denotes the element

$$x_{i_1}^{\varepsilon_1} x_{i_2}^{\varepsilon_2} \cdots x_{i_m}^{\varepsilon_m}, \qquad \varepsilon_j = \begin{cases} 1 & b_j = \mathrm{true}, \\ -1 & b_j = \mathrm{false}, \end{cases}$$

of the free group on $x_0, x_1, \dots$ (the empty list is the identity).

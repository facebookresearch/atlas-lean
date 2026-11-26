# Value of a group word under an assignment

For a group $G$, an assignment $x : \mathbb{N} \to G$ and a word $w = (i_1, b_1), \dots, (i_m, b_m)$ in the variables $x_0, x_1, \dots$ (the letter $(i, \mathrm{true})$ standing for $x_i$ and $(i, \mathrm{false})$ for $x_i^{-1}$), the value of $w$ is

$$w(x) = x(i_1)^{\varepsilon_1} \cdots x(i_m)^{\varepsilon_m} \in G, \qquad \varepsilon_j = \pm 1 \text{ according as } b_j = \mathrm{true} \text{ or } \mathrm{false},$$

the image of $w$ under the homomorphism from the free group on $x_0, x_1, \dots$ to $G$ sending $x_i$ to $x(i)$. The empty word has value $1$.

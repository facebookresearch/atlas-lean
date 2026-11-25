# The hybrid step

Let $H_0, H_1, \dots$ be games and $n \ge 1$. Let $D_0$ pick $i$ uniformly in $\{0, \dots, n - 1\}$
and play $H_i$, and let $D_1$ pick $i$ the same way and play $H_{i+1}$. Then

$$\mathrm{Adv}(D_0, D_1) = \frac{\mathrm{Adv}(H_0, H_n)}{n},$$

where $\mathrm{Adv}$ is the distinguishing advantage: picking the hybrid index uniformly keeps exactly
$1/n$ of the end-to-end advantage. This is the averaging step of Katz and Lindell's hybrid
arguments (Chapters 3 and 7).

# Cell-level grand mean

Let $\delta$ be a finite set of $D$ donors and $\kappa$ a finite set of $m$ cell slots, so that
every donor has $m$ cells $i = (d, c)$ (a balanced design). For cell values
$Y_i : \Omega \to \mathbb{R}$, the cell-level grand mean is

$$\bar Y(\omega) = \frac{1}{D m} \sum_{i \in \delta \times \kappa} Y_i(\omega).$$

With the convention $x / 0 = 0$ it is $0$ when there is no cell ($D = 0$ or $m = 0$).

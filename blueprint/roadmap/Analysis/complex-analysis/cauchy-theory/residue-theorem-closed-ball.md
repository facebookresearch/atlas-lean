# Residue theorem on a disc

Let $c\in\mathbb{C}$ and $R>0$, and let $S$ be a finite set of
points of the open disc $\{z:|z-c|\lt R\}$. For each $s\in S$ let $r_s>0$ be such that the closed
disc $\{z:|z-s|\le r_s\}$ lies in $\{z:|z-c|\lt R\}$ and contains no point of $S$ other than $s$.
Let $f:\mathbb{C}\to\mathbb{C}$ be complex differentiable on $\{z:|z-c|\le R\}\setminus S$ and
integrable on the circle $|z-c|=R$ and on each circle $|z-s|=r_s$. Then, with all circles
oriented counterclockwise,

$$\oint_{|z-c|=R} f(z)\,dz=\sum_{s\in S}\oint_{|z-s|=r_s} f(z)\,dz.$$

Each integral on the right is $2\pi i$ times the residue of $f$ at $s$.

## Sources

- Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable", entry "residue theorem"; L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §5.1 (the residue theorem).

# Itô integral of a Riemann step approximation

For a filtration $F$, $g : \mathbb{R} \to \mathbb{R}$, $t \ge 0$, $n \in \mathbb{N}$, a real process $B$ and every $\omega$, the
[elementary Itô integral](ito-integral.md) at time $t$ of the [left-point approximation](riemann.md) of $g$ is the
Itô–Riemann sum

$$\sum_{k < n} g\Bigl(\frac{tk}{n}\Bigr) \bigl( B_{t(k+1)/n} - B_{tk/n} \bigr) .$$

# Abel continuation of a Dirichlet series

For $f : \mathbb{N} \to \mathbb{C}$ with partial
sums $A(n) = \sum_{k=1}^{n} f(k)$, the Abel continuation of $f$ is the function
$F_f : \mathbb{C} \to \mathbb{C}$ given by

$$F_f(s) = s \int_1^\infty A(\lfloor t \rfloor)\, t^{-s-1}\, dt,$$

where the integral is taken to be $0$ when the integrand is not integrable on $(1, \infty)$.

# C¹ norm on a set

Let $E$ and $F$ be real normed spaces and let $\mu$ be a measure on $E$
(by default the volume measure). For a function $f : E \to F$ and a set $s \subseteq E$, write
$\mu_s$ for the restriction of $\mu$ to $s$. The $C^1$ norm of $f$ on $s$ is the extended
nonnegative real number

$$\|f\|_{C^1(s)} = \|f\|_{L^\infty(\mu_s)} + \|Df\|_{L^\infty(\mu_s)},$$

where $\|g\|_{L^\infty(\mu_s)}$ is the $\mu_s$-essential supremum of $\|g\|$, and $Df$ is the
Fréchet derivative of $f$ on all of $E$ (taken to be $0$ at points where $f$ is not
differentiable), a function from $E$ to the continuous linear maps $E \to F$, measured in the
operator norm.

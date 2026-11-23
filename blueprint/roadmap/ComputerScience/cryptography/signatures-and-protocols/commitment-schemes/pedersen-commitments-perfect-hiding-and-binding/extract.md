# Discrete-logarithm extractor from two openings

The extractor maps two openings $(m, r)$ and $(m', r')$ to $(m - m')(r' - r)^{-1}$ in $\mathbb{Z}/q$.
Here $u^{-1}$ is the inverse of $u$ in $\mathbb{Z}/q$ when $u$ is a unit, and otherwise a conventional
element of $\mathbb{Z}/q$ depending on $u$; in particular $0^{-1} = 0$, so the extractor gives $0$ when
$r = r'$. For $q$ prime and $r \neq r'$ it is $(m - m')/(r' - r)$.

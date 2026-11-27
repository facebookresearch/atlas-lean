# Derivative of a rotated vector

Let $n \in \mathbb{N}$, let $R : \mathbb{R} \to \mathbb{R}^{n \times n}$ satisfy $R(s)R(s)^{\mathsf T} = I$ for every $s$, let $t \in \mathbb{R}$, and assume every entry $s \mapsto R(s)_{ik}$ is differentiable at $t$. For a fixed vector $a \in \mathbb{R}^n$ let $r(s) = R(s)\,a$, and define the angular-velocity matrix

$$W_{ij} = \sum_{k} R'(t)_{ik}\, R(t)_{jk}.$$

Then for every index $i$,

$$r_i'(t) = \sum_j W_{ij}\, r_j(t).$$

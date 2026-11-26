# Error-correction update as an affine recurrence

For real numbers $\alpha$ and $\lambda$ and a real sequence $v : \mathbb{N} \to \mathbb{R}$, the following are equivalent:

- $v$ is an affine recurrence with slope $1 - \alpha$ and intercept $\alpha\lambda$, that is, $v_{n+1} = (1-\alpha)\,v_n + \alpha\lambda$ for every $n \in \mathbb{N}$;
- $v$ satisfies the error-correction update $v_{n+1} = v_n + \alpha(\lambda - v_n)$ for every $n \in \mathbb{N}$.

No condition is placed on $\alpha$ or $\lambda$.

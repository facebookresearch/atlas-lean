# Freezing one vertex keeps a 1/(eq) fraction of the colorings

Let $G$ have maximum degree $\Delta$, $b$ a proper $q$-coloring, $U \subseteq V$ and $v \in U$, and let $X_U$ be the proper colorings agreeing with $b$ off $U$. If $\Delta < q$ then

$$
\frac{|X_{U \setminus \{v\}}|}{|X_U|} \ge \frac{1}{q}\Bigl(1 - \frac{1}{q-\Delta}\Bigr)^{\Delta},
$$

and if $2\Delta < q$ this ratio is at least $1/(eq)$. The ratio equals the probability that a uniform element of $X_U$ colors $v$ with $b(v)$.

## Proof sketch

Start from the uniform law on $X_U$ and apply heat-bath updates at the neighbors of $v$ in $U$ and then at $v$; each update preserves the uniform law. Each neighbor update avoids $b(v)$ with probability at least $1 - 1/(q-\Delta)$, and once no neighbor carries $b(v)$ the update at $v$ chooses $b(v)$ with probability at least $1/q$.

## Depends on

- [Glauber dynamics for proper colorings with a frozen boundary](glauber-dynamics-for-colorings.md)

## Proof depends on

- [Rapid mixing of Glauber dynamics for colorings when q > 2 Delta](glauber-coloring-rapid-mixing.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.

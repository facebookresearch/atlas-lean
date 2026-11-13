# Stationary random functions (Slutsky–Khinchin)

Let $\mu$ be a measure on a measurable
space $\Omega$, and let $v$ assign to each real $t$ a function $v_t : \Omega \to \mathbb{R}$.
Then $v$ is stationary if there are a real number $c$ and a function $R : \mathbb{R} \to \mathbb{R}$
such that for all real $t$ and $h$, $\int v_t \, d\mu = 0$, $\int v_t^2 \, d\mu = c$ and
$\int v_t \, v_{t+h} \, d\mu = R(h)$.

The integrals are Bochner integrals, which are $0$ for non-integrable functions, so integrability
of $v_t$, $v_t^2$ and $v_t v_{t+h}$ is not required.

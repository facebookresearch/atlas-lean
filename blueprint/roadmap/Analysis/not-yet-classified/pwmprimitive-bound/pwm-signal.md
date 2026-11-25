# PWM switching signal

For a carrier (switching-cycle) length $\varepsilon$ and a duty function $d : \mathbb{R} \to \mathbb{R}$, the left-endpoint-sampled PWM signal is
$$s_\varepsilon(t) = \begin{cases} 1 & \text{if } t - k\varepsilon < d(k\varepsilon)\,\varepsilon, \\ 0 & \text{otherwise}, \end{cases} \qquad k = \lfloor t/\varepsilon \rfloor.$$
For $\varepsilon > 0$ this is $1$ on $[k\varepsilon, k\varepsilon + d(k\varepsilon)\varepsilon)$ and $0$ on the rest of the cycle $[k\varepsilon, (k+1)\varepsilon)$. For $\varepsilon = 0$ the formula takes the convention $t/0 = 0$, so $k = 0$ and $s_0(t) = 1$ exactly when $t < 0$.

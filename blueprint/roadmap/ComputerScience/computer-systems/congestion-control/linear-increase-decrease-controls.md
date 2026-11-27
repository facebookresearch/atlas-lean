# Linear increase/decrease controls

In the model of Chiu and Jain, $n$ users share one bottleneck resource in discrete time slots. In slot $t$ user $i$ has load $x_i(t) \ge 0$, the total load is $X(t) = \sum_i x_i(t)$, and the state of the system is the vector $x(t) = (x_1(t), \dots, x_n(t))$. At the end of the slot the resource sends every user the same binary feedback $y(t)$: $y(t) = 0$ asks the users to increase their load and $y(t) = 1$ to decrease it; the resource sets it by comparing the total load with a goal $X_{goal}$, the load at its knee. Each user changes its load using only its own previous load and the feedback. A *linear control* with parameters $a_I, b_I, a_D, b_D$ is

$$
x_i(t+1) =
\begin{cases}
a_I + b_I\, x_i(t) & \text{if } y(t) = 0 \text{ (increase)}, \\
a_D + b_D\, x_i(t) & \text{if } y(t) = 1 \text{ (decrease)} .
\end{cases}
$$

Special cases are *additive increase, multiplicative decrease* (AIMD: $a_I > 0$, $b_I = 1$, $a_D = 0$, $0 < b_D < 1$), multiplicative increase and decrease ($a_I = a_D = 0$, $b_I > 1$, $0 < b_D < 1$), additive increase and decrease ($b_I = b_D = 1$, $a_I > 0 > a_D$), and multiplicative increase, additive decrease. The system is *efficient* when $X(t)$ is close to $X_{goal}$, and it *converges to fairness* when the [fairness index](jain-s-fairness-index.md) $F(x(t))$ tends to $1$.

## Depends on

- [Jain's fairness index](jain-s-fairness-index.md)

## Sources

- D.-M. Chiu and R. Jain, "Analysis of the increase and decrease algorithms for congestion avoidance in computer networks", *Computer Networks and ISDN Systems* 17(1):1–14, 1989, Section 1.3 (the model of Fig. 2, the binary feedback and equations (1)–(2) with the four examples of linear controls) and Section 1.4 (the efficiency and convergence criteria).

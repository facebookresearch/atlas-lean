# Minimum-cost tool life

Let a cut of fixed length take machining time $\lambda/v$ at cutting speed $v > 0$, $\lambda > 0$, and let the tool life follow
Taylor's law $v\,T^n = C$, that is $T(v) = (C/v)^{1/n}$, with $C > 0$ and $0 < n < 1$. With machine and labour rate $c_0 > 0$,
tool-change time $t_c \ge 0$ and tool cost $c_t \ge 0$, not both zero, the cost per part is

$$c(v) = c_0\,\frac{\lambda}{v} + (c_0 t_c + c_t)\,\frac{\lambda/v}{T(v)} .$$

It has a unique minimizer on $v > 0$, at which the tool life is $T^* = \bigl(\frac1n - 1\bigr)\bigl(t_c + c_t/c_0\bigr)$ and the speed
is $v^* = C/(T^*)^n$: the derivative is $\lambda v^{-2}\bigl(-c_0 + (c_0 t_c + c_t)(\frac1n - 1)/T(v)\bigr)$, whose bracket increases
in $v$.

## Depends on

## Proof depends on

## Expansion

Open a source for Taylor's tool-life law and the minimum-cost tool life, and check the cost model and its domain against it.

## Sources

- F. W. Taylor, On the art of cutting metals, *Transactions of the American Society of Mechanical Engineers* 28 (1907) 31–350.

# Closed-loop gain $A/(1 + A\beta)$ of a finite-gain feedback amplifier

For real numbers $A$ and $\beta$, the closed-loop gain of the finite-gain feedback amplifier with
open-loop gain $A$ and feedback factor $\beta$ is

$$G(A, \beta) = \frac{A}{1 + A\beta} .$$

With the convention $x / 0 = 0$, it is $0$ when $A\beta = -1$. In the amplifier model $A > 0$ and
$\beta > 0$, so that [$1 + A\beta > 0$](one-add-mul-pos.md). There $G(A, \beta)$ is the factor
multiplying the input in the [closed-form output](eq-closed-form-of-eq.md) of the amplifier equation
$v_o = A (v_i - \beta v_o)$, and it is positive and
[below the ideal gain $1/\beta$](closed-loop-gain-pos-and-lt.md).

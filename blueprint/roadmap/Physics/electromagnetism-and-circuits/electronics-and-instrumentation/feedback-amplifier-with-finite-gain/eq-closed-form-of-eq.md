# For $A, \beta > 0$ any amplifier-equation solution is the closed form

Let $A > 0$ and $\beta > 0$ be the open-loop gain and the feedback factor of a finite-gain
negative-feedback amplifier, and let the real numbers $v_i$ (input) and $v_o$ (output) satisfy the
amplifier equation

$$v_o = A\,(v_i - \beta v_o),$$

in which $v_i - \beta v_o$ is the error between the input and the fed-back output. Then

$$v_o = \frac{A\, v_i}{1 + A\beta},$$

where the denominator $1 + A\beta$ is [positive](one-add-mul-pos.md). So for each input the
equation has at most one solution; the closed form [does solve it](../rail-limited-feedback-amplifier/linear-candidate-satisfies.md).

# Loaded DC gain $a b A_0/(1 + \beta b A_0)$

For real numbers $A_0$, $\beta$, $a$, $b$, the loaded DC gain is the real number

$$G_{DC} = \frac{a b A_0}{1 + \beta b A_0} .$$

With the convention $x / 0 = 0$, it is $0$ when $\beta b A_0 = -1$; that value comes from the
convention and is not a gain of the model. When $1 + \beta b A_0 \ne 0$, signals obeying the loaded
model at $s = 0$ satisfy $v_o = G_{DC}\, v_i$
([DC output of the loaded model](output-eq-loaded-dc-gain-mul-input.md)). In the model
$A_0, \beta > 0$ and the dividers $a, b$ are positive and at most $1$; then the denominator exceeds
$1$ and $0 < G_{DC} < a/\beta$ ([bounds on the DC gain](loaded-dc-gain-pos-and-lt.md)). For every
parameter choice $G_{DC}$ is the value at $s = 0$ of the
[loaded closed-loop transfer](loaded-transfer.md), and $a$ times the
[closed-loop gain](closed-loop-gain.md) of the load-referred open-loop gain $b A_0$.

# Feedback amplifier with finite gain

## The finite-gain feedback law

- [For $A, \beta > 0$ the loop denominator $1 + A\beta$ is positive](one-add-mul-pos.md)
- [For $A, \beta > 0$ any amplifier-equation solution is the closed form](eq-closed-form-of-eq.md)
- [For $A, \beta > 0$ the closed form solves the amplifier equation](closed-form-satisfies.md)
- [Closed-loop gain $A/(1 + A\beta)$ of a finite-gain feedback amplifier](closed-loop-gain.md)
- [For $A, \beta > 0$ the output is the closed-loop gain times the input](output-eq-closed-loop-gain-mul.md)
- [For $A, \beta > 0$ the gain deficit is $1/(\beta(1 + A\beta))$](gain-deficit.md)
- [For $A, \beta > 0$ the closed-loop gain lies in $(0, 1/\beta)$](closed-loop-gain-pos-and-lt.md)

## Source and load dividers

- [Source divider $R_{in}/(R_s + R_{in})$](source-divider.md)
- [Load divider $R_L/(R_o + R_L)$](load-divider.md)
- [Source divider is positive and at most 1 for $R_{in} > 0$, $R_s \ge 0$](source-divider-pos-and-le-one.md)
- [Load divider is positive and at most 1 for $R_L > 0$, $R_o \ge 0$](load-divider-pos-and-le-one.md)

## One-pole open-loop and loaded transfer

- [One-pole open-loop response $A_0/(1 + s/\omega_p)$](open-loop-gain.md)
- [Loaded closed-loop transfer $a b A_0/(1 + s/\omega_p + \beta b A_0)$](loaded-transfer.md)
- [Away from denominator zeros the loaded model gives $v_o = G(s)\,v_i$](output-eq-loaded-transfer-mul-input.md)

## Loaded DC gain

- [Loaded DC gain $a b A_0/(1 + \beta b A_0)$](loaded-dc-gain.md)
- [At $s = 0$ the loaded transfer equals the loaded DC gain](loaded-transfer-zero.md)
- [If $1 + \beta b A_0 \ne 0$, the DC output is the DC gain times $v_i$](output-eq-loaded-dc-gain-mul-input.md)
- [Loaded DC gain is $a$ times the closed-loop gain of $b A_0$](loaded-dc-gain-eq-source-divider-mul-clo.md)
- [For positive $A_0, \beta, a, b$ the DC gain lies in $(0, a/\beta)$](loaded-dc-gain-pos-and-lt.md)

## Denominator zero and its location

- [Closed-loop pole location $-\omega_p(1 + \beta b A_0)$](closed-loop-pole.md)
- [For $\omega_p > 0$ the pole location is the only denominator zero](denominator-eq-zero-iff.md)
- [For positive parameters the closed-loop pole location is negative](closed-loop-pole-neg.md)
- [For positive parameters no denominator zero has $\mathrm{Re}\,s \ge 0$](denominator-ne-zero-of-re-nonneg.md)

## Lossless dividers and a worked example

- [With zero source and output resistance both dividers equal 1](dividers-eq-one-of-no-source-output-resi.md)
- [At $a = b = 1$, $G(s) = A_0/(1 + s/\omega_p + \beta A_0)$](loaded-transfer-at-unit-dividers.md)
- [Example: halved dividers, $A_0 = 10$, $\beta = 1$, $\omega_p = 2$](loaded-example.md)

# Pascal recurrence for mixed moments on the unit interval

For a finite measure $\mu$ on the unit interval $[0, 1]$ and natural numbers $a$ and $b$, the [mixed moment](unit-interval-moment.md) is $m_{a,b}(\mu) = \int_{[0,1]} x^a (1 - x)^b \, d\mu(x)$. Then

$$m_{a,b}(\mu) = m_{a,b+1}(\mu) + m_{a+1,b}(\mu),$$

obtained by integrating $x^a (1 - x)^b = x^a (1 - x)^{b+1} + x^{a+1} (1 - x)^b$, which is $1 = (1 - x) + x$ multiplied by $x^a (1 - x)^b$.

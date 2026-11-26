# IEEE values of a binary format

The values of a binary format $F$ are a single quiet NaN
(the model is canonical-NaN: NaN carries neither a sign nor a payload, and there is no signalling
NaN), the infinities $+\infty$ and $-\infty$, and the finite numbers $\pm m$, given by a sign bit
and a magnitude $m \ge 0$ that is a number of the format. A sign bit `true` means negative, so the
format has the two zeros $+0$ and $-0$.

## Sources

- IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.2; Boldo, Jourdan, Leroy and Melquiond, *Verified compilation of floating-point computations*, Journal of Automated Reasoning 54(2), 2015, Section 5.1.

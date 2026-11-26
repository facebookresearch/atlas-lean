# Four-outcome comparison

The comparison of two values of a binary format has four mutually
exclusive outcomes: less (`some .lt`), equal (`some .eq`), greater (`some .gt`) and unordered
(`none`). NaN is unordered with every value, itself included. Any other two values compare as
their values in the extended real line, with $-\infty$ below every finite number and $+\infty$
above, so $+0$ and $-0$ are equal. This is IEEE's quiet comparison, which raises no flag.

## Sources

- IEEE Std 754-2019, Clause 5.11; Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 3.2.2; Boldo, Jourdan, Leroy and Melquiond, *Verified compilation of floating-point computations*, Journal of Automated Reasoning 54(2), 2015, Section 6.3.

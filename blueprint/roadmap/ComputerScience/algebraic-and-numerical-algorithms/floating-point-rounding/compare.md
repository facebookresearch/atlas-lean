# Four-outcome comparison

Between two values of a binary format exactly one of four mutually
exclusive relations holds: less than, equal, greater than or unordered. This function returns which
one, as `some .lt`, `some .eq`, `some .gt` or `none`. NaN is unordered with every value, itself
included. Any other two values are related as their values in the extended real line, with
$-\infty$ below every finite number and $+\infty$ above, so $+0$ and $-0$ are equal.

IEEE 754's comparison predicates are Boolean tests of these relations, such as whether $a \le b$;
this function is not one of them but classifies the relation, and it returns no flags. The model
has a single quiet NaN and no signalling NaN, so it leaves out the invalid exception that a
comparison with a signalling NaN operand signals, whichever predicate is used.

## Sources

- IEEE Std 754-2019, Clause 5.11; Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 3.2.2; Boldo, Jourdan, Leroy and Melquiond, *Verified compilation of floating-point computations*, Journal of Automated Reasoning 54(2), 2015, Section 6.3.

# Normalizing a prime-exponent Fermat solution

Suppose $a,b,c$ are nonzero integers,
$p$ is a natural prime with $p\ge5$, and $a^p+b^p=c^p$. Then a Frey package exists: a tuple
of nonzero integers $a',b',c'$ satisfying the Fermat equation at a prime exponent at least five,
with $\gcd(a',b')=1$, $a'\equiv3\pmod4$, and $b'\equiv0\pmod2$. The conclusion is existence
of a package, without an explicit equality identifying its exponent with $p$.

## Sources

- The Frey–Serre proof strategy and the [Imperial College London Fermat project](https://github.com/ImperialCollegeLondon/FLT) for the normalized package and curve model; Anthropic's [Frey package normalization statement](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_of_counterexample.lean).

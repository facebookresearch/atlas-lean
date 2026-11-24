# Impossibility of virtual black-box obfuscation

There is no virtual black-box obfuscator for the class of all polynomial-size circuits. More precisely, if one-way functions exist then there is a family of efficiently computable functions that is unobfuscatable: some predicate of the function is efficiently computable from any circuit computing it but is hard to compute with only oracle access. Since an efficient virtual black-box obfuscator would itself imply one-way functions, the impossibility holds unconditionally.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](indistinguishability-and-virtual-black-box.md)
- [One-way function families](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- B. Barak, O. Goldreich, R. Impagliazzo, S. Rudich, A. Sahai, S. Vadhan and K. Yang, "On the (im)possibility of obfuscating programs", *Journal of the ACM* 59(2), Article 6, 2012, <https://www.boazbarak.org/Papers/obfuscate.pdf>

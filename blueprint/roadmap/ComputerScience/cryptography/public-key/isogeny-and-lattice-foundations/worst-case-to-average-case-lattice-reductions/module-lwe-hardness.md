# Worst-case hardness of Module-LWE

For a cyclotomic ring $R$ of degree $n$, module rank $d$, polynomial modulus $q$ and error rate $\alpha$ with $\alpha q\ge\omega(\sqrt{\log(nd)})$, there is a quantum polynomial-time reduction from approximate $\mathrm{SIVP}$ (and $\mathrm{GapSVP}$) on module lattices of rank $d$ over $R$, with approximation factor $\mathrm{poly}(nd)/\alpha$, to search Module-LWE over $R_q^{d}$, and classical search-to-decision reductions as for Ring-LWE. Module-LWE interpolates between Ring-LWE ($d=1$) and LWE ($n=1$).

## Proof sketch

Generalize the Ring-LWE reduction by working with $R$-modules of rank $d$ in place of ideals; discrete Gaussians on module lattices give Module-LWE samples via the dual module, and the iterative quantum step carries over with the module structure.

## Depends on

- [Hardness of Ring-LWE from worst-case problems on ideal lattices](ring-lwe-hardness.md)

## Proof depends on

- [Hardness of Ring-LWE from worst-case problems on ideal lattices](ring-lwe-hardness.md)

## Sources

- Adeline Langlois, Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography (2015).

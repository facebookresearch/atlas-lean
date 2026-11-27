# Kernel of reduction modulo p on the p-adic integers

Let $p$ be a prime. Reduction modulo $p$ is the ring homomorphism $\mathbb{Z}_p \to \mathbb{Z}/p\mathbb{Z}$
that sends $x$ to the residue class of the unique natural number $n < p$ with $|x - n|_p < 1$. Its
kernel is the maximal ideal of the local ring $\mathbb{Z}_p$, the set of non-units, which is
$p\mathbb{Z}_p$.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter II,
  §1 (the ring $\mathbb{Z}_p$ and the field $\mathbb{Q}_p$; $p$-adic units in §1.2), pp. 11–13.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842:
  [PadicInt.ker_toZMod](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/Padics/RingHoms.lean#L326 "PadicInt.ker_toZMod"),
  with `PadicInt.toZMod` and `PadicInt.zmodRepr` in the same file; the maximal ideal is
  $p\mathbb{Z}_p$ by `PadicInt.maximalIdeal_eq_span_p`.

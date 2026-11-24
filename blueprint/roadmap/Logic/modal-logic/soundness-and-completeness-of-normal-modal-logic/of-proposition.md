# Translation of diamond-presentation formulas

Formulas of the diamond presentation of unimodal logic are translated into
modal formulas in the $\bot$, $\to$, $\Box$ basis by recursion, writing $\varphi'$ for the
translation of $\varphi$: an atom $p$ goes to $p$, falsehood to $\bot$, $\neg\varphi$ to
$\varphi' \to \bot$, $\varphi \lor \psi$ to $(\varphi' \to \bot) \to \psi'$, and the diamond applied to
$\varphi$ goes to $\Diamond\varphi'$, that is, to
$\Box(\varphi' \to \bot) \to \bot$.

## Sources

- CSLib, release v4.35.0, modal logic (<https://github.com/leanprover/cslib/tree/v4.35.0/Cslib/Logics/Modal>): the diamond presentation of unimodal logic, its models and its semantic logics K, T, S4 and S5.

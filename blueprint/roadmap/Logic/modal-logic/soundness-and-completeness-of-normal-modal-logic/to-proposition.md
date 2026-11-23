# Translation of modal formulas into the diamond presentation

Each modal formula built from
atoms, $\bot$, $\to$ and $\Box$ is translated into a formula of the diamond presentation by recursion:
an atom $p$ goes to the atom $p$, $\bot$ goes to false, $\varphi \to \psi$ goes to
$\neg\varphi' \lor \psi'$, and $\Box\varphi$ goes to $\neg\Diamond\neg\varphi'$, where
$\varphi'$ and $\psi'$ are the translations of $\varphi$ and $\psi$ and $\Diamond$ is the
diamond of the diamond presentation.

## Sources

- CSLib, release v4.35.0, modal logic (<https://github.com/leanprover/cslib/tree/v4.35.0/Cslib/Logics/Modal>): the diamond presentation of unimodal logic, its models and its semantic logics K, T, S4 and S5.

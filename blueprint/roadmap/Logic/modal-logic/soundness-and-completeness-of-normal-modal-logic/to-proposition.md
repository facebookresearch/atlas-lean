# Translation of modal formulas into CSLib propositions

Each modal formula built from
atoms, $\bot$, $\to$ and $\Box$ is translated into a CSLib unimodal proposition by recursion:
an atom $p$ goes to the atom $p$, $\bot$ goes to false, $\varphi \to \psi$ goes to
$\neg\varphi' \lor \psi'$, and $\Box\varphi$ goes to $\neg\Diamond\neg\varphi'$, where
$\varphi'$ and $\psi'$ are the translations of $\varphi$ and $\psi$ and $\Diamond$ is the
possibility operator of CSLib's unimodal language.

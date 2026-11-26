# Base change of graded Cartier module data

For a ring homomorphism `φ : B →+* B'` and
graded Cartier module data `D` over `B` (with `j`) and `D'` over `B'` (with `φ.comp j`), an
additive map `f : D.M →+ D'.M` is a base change along `φ` when
`f (w • x) = WittVector.map φ w • f x`, `f` commutes with `F`, `V` and `ϖ`, maps each piece of
`D` into the same piece of `D'`, and sends some homogeneous `V`-basis of `D` to a homogeneous
`V`-basis of `D'`.

# Structure constants of `ϖ` on the Cartier module

For a formal `O_D`-module `X` over `B`,
`γ : Fin 2 → M` in the Cartier module `M` of `X` and `a : ℕ → Fin 2 → B`: for every `i` and every
`N`, `ϖ (γ i) = ∑_{m < N} V^m (homothety (a m i) (γ (piIndex m i))) + V^N h` for some `h`, where
`ϖ` acts by `endAct X.varpiEnd`, `V` is `verschiebungInt` and `piIndex` is
`GradedCartierModuleData.piIndex`. This is the expansion of
`GradedCartierModuleData.HasStructureConstants`, with `homothety (a m i)` for the action of the
Teichmüller representative `[a m i]`, stated on the Cartier module, so it needs no complementary
graded pieces.

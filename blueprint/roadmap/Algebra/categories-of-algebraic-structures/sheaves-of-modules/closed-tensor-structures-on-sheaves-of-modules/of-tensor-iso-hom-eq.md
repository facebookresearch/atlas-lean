# Forward restriction tensor map as a counit chain

Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over `X`. Write `L=sheafificationBase`, `T=sheafificationOver`, `q=restrictPresheaf`, `F=restrictSheaf`, `U=forgetRestrictBase`, `e_A : T(q A) ≅ F(L A)` for `commIso`, and `c_M : L(U M) ≅ M` for the counit. For `A=U M`, `B=U N`, let `χ : F(M ⊗ N) ≅ F(M) ⊗ F(N)` be the composite
`F(c_M⁻¹ ⊗ c_N⁻¹) ≪≫ F(μ_L(A,B)) ≪≫ e_{A⊗B}⁻¹ ≪≫ T(μ_q(A,B))⁻¹ ≪≫ μ_T(q A,q B)⁻¹ ≪≫ (e_A ⊗ e_B) ≪≫ (F(c_M) ⊗ F(c_N))`.
Here `μ_L` and `μ_T` are the localized monoidal tensor isomorphisms.

Then `(ofTensorIso R X M N).hom = χ.hom`, as morphisms from `F(M ⊗ N)` to `F(M) ⊗ F(N)`.

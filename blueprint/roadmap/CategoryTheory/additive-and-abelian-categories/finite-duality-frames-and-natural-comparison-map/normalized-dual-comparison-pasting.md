# Pasting law for normalized dual comparisons

Consider categories C,D,A,B,A′,B′ and functors
P:C → D, R:C → A, S:D → B, Q:A → B,
R′:A → A′, S′:B → B′, Q′:A′ → B′, R₁:C → A′, S₁:D → B′.
Take squares ρ:S∘P ≅ Q∘R, ρ′:S′∘Q ≅ Q′∘R′,
ρ₁:S₁∘P ≅ Q′∘R₁ and δ_R:R′∘R ≅ R₁, δ_S:S′∘S ≅ S₁.
Let G,H,J,K,J′,K′ be the six contravariant functors and η_X the natural
comparison X∘dual_source ≅ dual_target∘Xᵒᵖ for
X=R,S,R′,S′,R₁,S₁. At M choose c:Q(J(R(M))) ≅ K(Q(R(M))),
c′:Q′(J′(R′(R(M)))) ≅ K′(Q′(R′(R(M)))), and
c₁:Q′(J′(R₁(M))) ≅ K′(Q′(R₁(M))).

Assume the following compatibility equations, using forward maps:

ρ₁,N=Q′(δ_R,N)∘ρ′,RN∘S′(ρ_N)∘δ_S,PN⁻¹ for every N;
η_R′,RM∘R′(η_R,M)=J′(δ_R,Mᵒᵖ)∘η_R₁,M∘δ_R,GM;
η_S′,SPM∘S′(η_S,PM)=K′(δ_S,PMᵒᵖ)∘η_S₁,PM∘δ_S,HPM;
η_S′,QRM∘S′(c)=K′(ρ′,RMᵒᵖ)∘c′∘Q′(η_R′,RM)∘ρ′,JRM;
c′∘Q′(J′(δ_R,Mᵒᵖ))=K′((Q′(δ_R,M))ᵒᵖ)∘c₁.

Then normalization around the outer square equals
δ_S,HPM∘S′(E_M)∘δ_S,PGM⁻¹, where E_M is the normalized comparison
for the first square and c.

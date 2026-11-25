# Homology inclusion into a split degree

Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. Let tᵢ : Hᵢ → Zᵢ
be its homology-to-cycles section and ℓᵢ : Hᵢ → Kᵢ its homology inclusion. For e : Kᵢ ≅ (Bᵢ ⊞
Hᵢ) ⊞ Qᵢ, the inverse restricted to homology is biprod.inr ≫ biprod.inl ≫ e.inv = ℓᵢ : Hᵢ →
Kᵢ, the inclusion constructed from s.normalize.

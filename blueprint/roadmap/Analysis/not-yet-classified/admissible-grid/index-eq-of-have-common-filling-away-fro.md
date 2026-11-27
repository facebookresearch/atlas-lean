# Common-filling support gives equal winding indices off both traces

Let `D,H` be
finite grid fillings with positive, possibly different, scales. Write
`m_D(z),m_H(z)∈{0,1}` for the selected-cell indicators at each filling's floor-based
owner, and `S={z∈ℂ | m_D(z)≠m_H(z)}`. If `closure(S)⊆G∖K`, `z∉G∖K`, and `z` lies on
neither reduced trace, then `D.toCycle.index(z)=H.toCycle.index(z)`. The trace exclusions
allow the discrete residue formula to identify each index with its multiplicity.

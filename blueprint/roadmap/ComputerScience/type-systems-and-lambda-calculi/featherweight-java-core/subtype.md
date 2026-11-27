# Subtyping

Subtyping $C <: D$ in a class table is the reflexive-transitive closure of the [direct superclass relation](direct-extends.md) (S-REFL, S-TRANS, S-CLASS): $C <: D$ when there is a chain $C = C_0, C_1, \dots, C_k = D$ with $k \ge 0$ in which each $C_i$ directly extends $C_{i+1}$. All declared edges count, including those of a later declaration of the same class name, which class lookup ignores.

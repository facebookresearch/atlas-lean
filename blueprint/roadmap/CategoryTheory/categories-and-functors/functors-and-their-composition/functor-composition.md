# Composite of two functors

Let $F\colon \mathsf{C} \to \mathsf{D}$ and $G\colon \mathsf{D} \to \mathsf{E}$ be functors between categories. Their *composite* $GF\colon \mathsf{C} \to \mathsf{E}$, also written $G \circ F$, sends each object $c$ of $\mathsf{C}$ to the object $G(Fc)$ of $\mathsf{E}$, and each morphism $f\colon c \to c'$ of $\mathsf{C}$ to the morphism $G(Ff)\colon G(Fc) \to G(Fc')$ of $\mathsf{E}$.

## Sources

- Emily Riehl, Category Theory in Context, Dover Publications, 2016.
- John C. Baez, *Applied Category Theory Course*, Lecture 41, "Composing Functors", 2018, https://math.ucr.edu/home/baez/act_course/lecture_41.html: the composite B ∘ A of functors A and B acts by (B ∘ A)(x) = B(A(x)) on objects and (B ∘ A)(f) = B(A(f)) on morphisms.

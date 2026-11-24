# Pullback

Pullback transport of a fixed-fiber presentation.

Given `h` on `p : E ⟶ B` and a pullback square `sq` presenting `q : P ⟶ B'`
over `p` along `f : B' ⟶ B`, this returns the presentation of `q` with the
same fiber `F` and second projection `s ≫ h.r`. Only the given square and
the parent product limit are used.

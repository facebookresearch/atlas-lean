# Hurwitz Step

One directed right-Hurwitz step with explicit context: `pre ++ [a, b] ++ suf`
rewrites to `pre ++ [b, conjLabel b a] ++ suf`. Only the right move is exposed
because it alone bubbles a mover past a fixer in the point-elimination proof.
Purpose: atomic product-preserving move. Nonclaims: no reverse, left, symmetric
closure, or Coxeter abstraction.

# Joint likelihood of a sequence and a motif occurrence

The joint likelihood of a sequence `x` and a latent occurrence `z` with prior `prior z` and
start `start z` (`none`: no occurrence): background letters outside the window, site-model letters
inside. One occurrence per sequence (OOPS) is `Z = Fin (n + 1)`, `start = some`, `prior` uniform;
zero or one (ZOOPS) is `Z = Option (Fin (n + 1))`, `start = id`, `prior none = 1 - γ` and
`prior (some j) = γ / (n + 1)` for a fixed `γ`. The background `q` is a fixed parameter.

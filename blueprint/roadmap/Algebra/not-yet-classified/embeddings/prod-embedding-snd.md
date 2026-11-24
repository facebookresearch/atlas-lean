# Prod Embedding Snd

Embedding `FGModuleCat S ⥤ FGModuleCat (R × S)` via `RingHom.snd`.

An `S`-module `M` is regarded as an `(R × S)`-module by `(r,s) • m = s • m`.
This is `restrictScalars` along `snd`, using that `snd` is finite.

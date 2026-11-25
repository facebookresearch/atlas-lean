# Locally Surjective over Map

Local surjectivity is preserved by `overMap` along an arrow of the base
site. This mirrors `locallySurjective_over` (which handles `overFunctor`,
i.e. pushforward along `Over.forget`); here we push forward along `Over.map g`.
Both are `Presheaf.isLocallySurjective_whisker` for the cocontinuous
`Over.forget` / `Over.map` functors.

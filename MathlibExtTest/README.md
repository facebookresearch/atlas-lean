# MathlibExtTest

`MathlibExtTest` contains tests, benchmarks, and diagnostics for public
`MathlibExt` APIs. It may import `MathlibExt`, but production libraries must
not import it.

Tests should exercise meaningful public behavior, including boundary values,
typeclass inference, simplification, and expected elaboration failures when
those protect against plausible regressions.

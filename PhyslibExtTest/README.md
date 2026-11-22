# PhyslibExtTest

`PhyslibExtTest` contains tests and diagnostics for public `PhyslibExt` APIs. It
may import `PhyslibExt`, `CSLibExt`, and `MathlibExt`, but production libraries
must not import it.

Tests should exercise meaningful public behavior, including non-vacuity
witnesses for new predicates, boundary values, simplification, and expected
elaboration failures when those protect against plausible regressions.

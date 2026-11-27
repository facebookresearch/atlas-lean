# Discrete Stokes equality for a finite grid filling

Let `E` be a complete complex
normed vector space. Let `D` be a finite grid filling of scale `t>0`. For every `f:ℂ→E`,
the sum of its counterclockwise selected-cell boundary integrals equals the reduced
signed-edge integral: `D.toCycle.integral(f)=D.reducedIntegral(f)`. Internal edges cancel,
without a continuity hypothesis on `f`.

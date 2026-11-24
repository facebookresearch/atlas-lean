# Pending Runs Correct allows wrong suffix but scan Remainder rejects

Anti-vacuity regression for the new invariant: the previously approved
pending-run predicate genuinely permits a wrong unscanned suffix, while
`ScanRemainderMatches` rejects that same concrete state.

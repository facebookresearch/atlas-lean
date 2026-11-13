# Log-odds Viterbi is linear-gap Needleman–Wunsch

For a memoryless pair HMM whose
per-column log-odds scores are `σ a b` and `gap`, the log-odds Viterbi score against the
independence model is the Needleman–Wunsch score with substitution scores `σ` and linear gap
score `gap`, plus the length term `log (τ / η²)`.

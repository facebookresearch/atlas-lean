# Debt payoff plus the equity call payoff equals the firm value

For all real firm values `V` and face values `F`, debt plus equity reconstructs the firm:
`min(V, F) + max(V - F, 0) = V`. Equity is the European call payoff `max(V - F, 0)` on firm value
struck at the face value (limited liability), and debt is the payoff `min(V, F)`.

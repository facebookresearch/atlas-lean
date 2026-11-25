# Erasing a role preserves the guard condition

Let $\Delta$ be an ownership context, $e$, $z$ endpoints and $k$ a natural number. If
$\mathrm{Min}_\Delta(e,k)$ holds (every endpoint $d \ne e$ with an active capability in $\Delta$ has
rank $> k$), then $\mathrm{Min}_{\Delta \setminus z}(e,k)$ holds, where $\Delta \setminus z$ is
$\Delta$ with the entry of $z$ removed.

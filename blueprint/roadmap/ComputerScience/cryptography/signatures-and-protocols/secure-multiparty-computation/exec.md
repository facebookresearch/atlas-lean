# One-exchange execution law

There are three wired roles, labelled 0 (environment), 1 (intermediary) and 2 (main party).
Messages contain no address or apparent-sender field. The environment chooses an API input to
party 2, a command to intermediary 1 and a private table on the two return bits. Only it reads
$z$. The intermediary's closed program turns the command into a backdoor input and a private
return table. The party's closed program takes the API and backdoor inputs and replies on both
ports. Apply the intermediary's return table to the backdoor reply and the environment's table
to the API reply and that report. The result is a probability mass function on the final bit;
all three programs draw independent coins.

## Sources

- one-exchange specialization of R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC Summer School (2025), slides 17 and 20–21.
